#*****************************************************************************
#       Copyright (C) 2016 Liang Ge <liang.ge@gmail.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from sage.structure.sage_object import SageObject
from sage.rings.rational import Rational
from sage.all import *
import sys

Tensor=[[0,0], [0,1], [0,2], [1,0], [1,1], [1,2], [2,0], [2,1], [2,2]]

#Tensor2_Index=[[0,0],[0,1], [0,2], [1,0], [1,1], [1,2], [2,0],[2,1],[2,2]]

Tensor_to_Voigt = [0,4,8,5,2,1]
LSDyna = [[0,0], [1,1],[2,2], [0,1], [1,2], [0,2]]
Tensor_to_LSDyna = [0, 4, 8, 1, 5, 2]

#OutputIndex_LSDyna=[0, 4, 8, 1, 5, 2]
#OutputIndex_Voigt=[0, 4, 8, 5, 2, 1]
#OutputIndex_FEAP=[0, 4, 8, 1, 5, 2]

#Idx={'xx':(0,0), 'xy':(0,1), 'xz':(0,2),
#    'yx':(1,0), 'yy':(1,1), 'yz':(1,2),
#    'zx':(2,0), 'zy':(2,1), 'zz':(2,2)}
Idx={'xx':0, 'xy':1, 'xz':2,
    'yx':3, 'yy':4, 'yz':5,
    'zx':6, 'zy':7, 'zz':8}

StressOutputFormat_Voigt  = ['xx', 'yy', 'zz', 'yz', 'xz', 'xy']
StressOutputFormat_LSDyna = ['xx', 'yy', 'zz', 'xy', 'yz', 'xz']
StressOutputFormat_FEAP   = ['xx', 'yy', 'zz', 'xy', 'yz', 'xz']
# Abaqus [11,22,33,12,13,23]
StressOutputFormat_Abaqus = ['xx', 'yy', 'zz', 'xy', 'xz', 'yz']

OutputFormat={'LSDyna':StressOutputFormat_LSDyna,
             'FEAP':StressOutputFormat_FEAP,
             'Abaqus':StressOutputFormat_Abaqus,
             'Voigt':StressOutputFormat_Voigt}

def I1(C):
    return C.trace()

def I2(C):
    return (Rational('1/2')*((C.trace())**2-(C**2).trace())).simplify_full()
    
def I3(C):
    return det(C)

def J2(C):
    return (Rational('1/2')*(C**2).trace())

def myindex(inV):
    return inV[0], inV[1]

def lambda_f(C, theta, phi):
    # This function returns the squre of 
    # fiber stretch after deformation    
        
    return ef(theta, phi)*C*ef(theta, phi)
    
def ef(theta, phi):
    # This returns the fiber orientation vector
    return vector([cos(theta), 
                   sin(theta)*cos(phi), sin(theta)*sin(phi)])

def rhom(theta, phi, b):
    # This function returns the pi periodic 
    # von Mises distribution
    # Note it is not normalized
    return exp(b*(cos(2*theta)+1))        

def list_to_fun(lst):
    fun=1
    for each in lst:
        fun*=each
    return fun

def separate(f, checkvar):
    from sage.symbolic.operators import mul_vararg
    import operator
    import functools
    if f.operator() == mul_vararg:
        ops=f.operands()
        ops_wvar=[1]+[gT for gT in ops if gT.has(checkvar)]
        ops_wovar=[1]+[gT for gT in ops 
                      if not gT.has(checkvar)]
        return (list_to_fun(ops_wvar), list_to_fun(ops_wovar))
    else:
        raise ValueError("Not a product!")

def I4_GST(C_in, b):
    """ 
    This function calculates the 4th invariant (a.k.a., GST invariant)
    # Input:
    #    C_in -- Right Cauchy-Green deformation tensor
    #    b -- controlling parameter for fiber dispersion
    # The mean fiber direciton is assumed to be aligned along the x direction
    # The fiber distribution rho=e^(b*(cos(2theta)+1))
    """

    from sage.symbolic.integration.integral import definite_integral

    var('theta, phi')
    wlambda=(lambda_f(C_in, theta=theta, phi=phi)
        *rhom(theta, phi, b=b)).simplify_full()

    e_int_phi=definite_integral(wlambda, phi, 0, 2*pi)

    # KKK here actually equals to 4*pi*K
    kkk=numerical_integral(rhom(theta, phi=0, b=b)
        *sin(theta), 0, pi)[0]*2*pi

    ops=e_int_phi.expand().operands()
    E_i=0
    for iop in ops:
        # separate each term into a part that can be numerically integrated and a part that can't be numerically integrated
        (fun_wvar, fun_wovar)=separate(iop, theta)

        tobeitgd=sin(theta)*fun_wvar

        itgd=numerical_integral(tobeitgd, 0, pi)[0]/kkk * fun_wovar
        E_i+=itgd

    return (E_i-1.)

def I4_GST_kappa(C_in):
    var('parKappa')
    E_i=parKappa*I1(C_in)+(1-3.*parKappa)*C_in[0,0]-1.
    return E_i

def I4_CH(C_in, b):
    r"""
    This function calculates the characteristic invariant
    Lazy bone version -- using numerical integral :)
    """
    from sage.symbolic.integration.integral import definite_integral

    var('theta, phi')
    wlambda=((lambda_f(C_in, theta=theta, phi=phi)-1)**2
        *rhom(theta, phi, b=b))

    e_int_phi=definite_integral(wlambda, phi, 0, 2*pi)

    # KKK here actually equals to 4*pi*K
    kkk=numerical_integral(rhom(theta, phi=0, b=b)
        *sin(theta), 0, pi)[0]*2*pi

    ops=e_int_phi.expand().operands()
    Lambda_i=0
    for iop in ops:
        # separate each term into a part that can be numerically integrated and a part that can't be numerically integrated
        (fun_wvar, fun_wovar)=separate(iop, theta)

        tobeitgd=sin(theta)*fun_wvar
        itgd=numerical_integral(tobeitgd, 0, pi)[0]/kkk * fun_wovar
        Lambda_i+=itgd

    return Lambda_i

class umat(SageObject):
    r"""
    This class generate Fortran subroutines for user defined material laws from a symbolic expression of strain energy function

    AUTHORS:

    - Liang Ge (2015-03-01): initial version

    """


    def __init__(self, project='project', outfile='Test', outroutine='Test',
                 lang='F95', Implicit=False, MAT='Test', FEAFormat='Voigt', 
                 ElasticityTensor='Spatial', Viscoelastic=False,
                 ModelingGrowth=False):
        r"""
        This initializes the Class

        Input:
        project: the project name
        outfile: the Fortran file name to save the user material subroutine
        outroutine: the Fortran subroutine name
        Implicit: When Implicit==True, the tangent matrix will be created in outfileImp.f90 file
        """

        self.project=project
        self.outfile=outfile
        self.outroutine=outroutine
        self.CauchyStress=False
        self.Imp=Implicit
        self.lang=lang
        self.ElasticityTensor=ElasticityTensor
        self.OutputFormat=OutputFormat[FEAFormat]
        self.OutputIdx=self.get_OutputIdx();
        self.Viscoelastic=Viscoelastic
    	self.ModelingGrowth=ModelingGrowth
        self.verbose=True
        
        self._initial_vars()
        if (Viscoelastic):
            self.initial_ratevars()

        if (ModelingGrowth):
            self.initial_growthvars()


        if (FEAFormat=='LSDyna'):
            self.ElasticityTensor='Spatial'
            
        return

    def get_OutputIdx(self):
        return [Idx[self.OutputFormat[ni]] for ni in xrange(6)]

    def _initial_vars(self):

        self.C=matrix(SR, 3, 3, var('C11, C12, C13, C21, C22, C23, C31, C32, C33'))

        # Deformation gradient tensor
        self.F=matrix(SR, 3, 3, var('F11, F12, F13, F21, F22, F23, F31, F32, F33'))

        self.jacC=self.C.det()
        self.jacF=sqrt(self.jacC)
        self.Jacobian=self.jacF

        # Green-Lagrangian strain tensor
        self.E=Rational('1/2')*(self.C-matrix.identity(3))

        # Isochoric deformation tensor
        self.C_Bar=self.Jacobian**Rational('-2/3')*self.C
        self.Z=0
        return

    def initial_ratevars(self):
        self.dC=matrix(SR, 3, 3, var('dC11, dC12, dC13, dC21, dC22, dC23, dC31, dC32, dC33'))

        self.dd=matrix(SR, 3, 3, var('dd11, dd12, dd13, dd21, dd22, dd23, dd31, dd32, dd33'))

        self.W_visc=0
        return

    def initial_growthvars(self):
        r"""
        Define auxially variables for growth modeling
        """
        self.Cg=matrix(SR, 3, 3, var('Cg11, Cg12, Cg13, Cg21, Cg22, Cg23, Cg31, Cg32, Cg33'))

        self.Fg=matrix(SR, 3, 3, var('Fg11, Fg12, Fg13, Fg21, Fg22, Fg23, Fg31, Fg32, Fg33'))

        self.Fg_inv=self.Fg.inverse().simplify_rational()

        self.Fg_user=0

        # Elastic part of deformation tensor
        self.Ce=self.Fg_inv.transpose()*self.C*self.Fg_inv
        # Elastic deformation gradient tensor
        self.Fe=self.F*self.Fg_inv

        self.jacCe=self.Ce.det()
        self.jacFe=sqrt(self.jacCe)
        self.Jacobian_e=self.jacFe.simplify_rational()

        # Isochoric deformation tensor
        self.Ce_Bar=self.Jacobian_e**Rational('-2/3')*self.Ce

        return

    def _strainenergy_(self):
        pass

    def _construct_SE_(self, MAT='Fung'):
        self.W=0

    def substitute_tensor(self, mtx_func_in, oldT, newT):
        mtx_func_out=copy(mtx_func_in)
        for nr in xrange(mtx_func_in.nrows()):
            for nc in xrange(mtx_func_in.ncols()):
                mtx_func_out[nr,nc]=self.substitute_components(mtx_func_out[nr,nc], oldT, newT)
        return mtx_func_out

    def substitute_components(self,func_in, lhs, rhs):
        lhs_list=lhs.list()
        rhs_list=rhs.list()
        func_out=copy(func_in)
        for ni in xrange(len(lhs_list)):
            func_out=func_out.substitute(lhs_list[ni]==rhs_list[ni])
        return func_out


    def calc_cauchy_stress(self):
        r"""
        This function calculates the Cauchy stress tensor from the strain energy function
        """
        from sympy import Matrix as Mtx_Sympy

        if (self.W==0):
            print 'Strain energy function was not defined!'
            return

        if (self.verbose):
            print 'Calculating 2nd Piola Kirchoff Stress'
            sys.stdout.flush()
            
        S_PK=jacobian(self.W, self.C.list())*2

        # Substitute C=F^T*F
        self.CC=self.F.transpose()*self.F

        tmp=copy(S_PK.list())
        for i in xrange(9):
            tmp[i]=tmp[i].substitute([self.C.list()[li]==self.CC.list()[li] for li in xrange(9)])
        S_PK_Sympy=Mtx_Sympy(3, 3, tmp)

        F_Sympy=Mtx_Sympy(3, 3, self.F.list())

        # Form the 2nd Piola-Kirchoff stress tensor
        self.S_PK=matrix(SR, 3, 3, S_PK.list())


        # Push forward the 2nd PK stress tensor to obtain the Cauchy stress tensor
        self.Sigma=(self.F)*self.S_PK*transpose(self.F)*self.Jacobian**(-1)

        Sigma_Sympy=F_Sympy*S_PK_Sympy*F_Sympy.T*(
            (self.Jacobian.substitute([self.C.list()[li]==
                                       self.CC.list()[li] for li in xrange(9)]))._sympy_())**(-1)


#        SigmaTMP=copy(self.Sigma)
        #matrix(SR, 3, 3, [0 for i in xrange(9)])
#        for ni in xrange(3):
#            for nj in xrange(3):
#        		SigmaTMP[ni,nj]=(self.Sigma[ni,nj].substitute([self.C.list()[li]==self.CC.list()[li] for li in xrange(9)]))

        # Remove the redudunt stress terms and store in FEA specific format
        # Could be Voigt format or LSDyna format
        self.Sigma_FEA=self.tensor_2_to_FEA_Sympy(Sigma_Sympy)
        self.CauchyStress=True
        return

    def calc_cauchy_stress_growth(self):
        import sys, time
        r"""
        This function calculates the Cauchy stress tensor after growth from the strain energy function
        """
        from sympy import Matrix as Mtx_Sympy

        self.calc_cauchy_stress()
        return 0
        if (self.W==0):
            print 'Strain energy function was not defined!'
            return

        # The C_prime matrix is defined here to help calculate dC/dC_e
        C_prime=self.Fg.transpose()*self.C*self.Fg

        S_PK=matrix(SR, 3, 3, [0 for i in xrange(9)])

        S_PK_Sympy=Mtx_Sympy(3,3,[0 for i in xrange(9)])
        SigmaTMP=Mtx_Sympy(3,3,[0 for i in xrange(9)])

        print 'Step0'
        sys.stdout.flush()

        # Substitute C=F^T*F
        self.CC=self.F.transpose()*self.F

        for i in xrange(3):
            for j in xrange(3):
                S_PK[i,j]=0
                S_PK_Sympy[i,j]=0

        for k in xrange(3):
            print 'k',k
            sys.stdout.flush()
            start = time.time()

            for l in xrange(3):
                comp=self.W.diff(self.C[k,l])*2
                comp_expd=(comp.substitute([self.C.list()[ni]==self.CC.list()[ni] for ni in xrange(9)]))._sympy_()
                #(self.substitute_components(comp, self.C, self.CC))._sympy_()
                for i in xrange(3):
                    for j in xrange(3):
                        S_PK[i,j]+=comp*C_prime[k,l].diff(self.C[i,j])
                        SigmaTMP[i,j]+=comp_expd*((C_prime[k,l].diff(self.C[i,j])).
                                                  substitute([self.C.list()[ni]==self.CC.list()[ni] for ni in xrange(9)]))._sympy_()
            end = time.time()
            print(end - start)
            sys.stdout.flush()

        S_PK_Sympy=SigmaTMP

        print 'Step1'
        sys.stdout.flush()

        self.S_PK_span=S_PK.list()

        # Form the 2nd Piola-Kirchoff stress tensor
        self.S_PK=matrix(SR, 3, S_PK.list())

        # Push forward the 2nd PK stress tensor to obtain the Cauchy stress tensor
        # sigma = Fe * S_PK * Fe^T / J_e
        self.Sigma=(self.Fe)*self.S_PK*transpose(self.Fe)*self.Jacobian_e**(-1)

        Fe_Sympy=Mtx_Sympy(3,3,self.Fe.list())

        SigmaTMP=Fe_Sympy*S_PK_Sympy*Fe_Sympy.T*(
            ((self.Jacobian_e.substitute([self.C.list()[ni]==self.CC.list()[ni] for ni in xrange(9)]))**(-1))._sympy_())

        print type(SigmaTMP)
        sys.stdout.flush()

        #(self.Fe)*SigmaTMP*transpose(self.Fe)*self.Jacobian_e**(-1)
        print 'Step2', type(SigmaTMP)
        sys.stdout.flush()

        # Remove the redudunt stress terms and store in FEA specific format
        # Could be Voigt format or LSDyna format

        self.Sigma_FEA=self.tensor_2_to_FEA_Sympy(SigmaTMP)
        #self.tensor_to_FEA(Mtx_Sympy(SigmaTMP))
        self.CauchyStress=True
        print 'Step3'
        sys.stdout.flush()
        return
    
    def calc_cauchy_stress_growth_vold(self):
        import sys, time
        r"""
        This function calculates the Cauchy stress tensor after growth from the strain energy function
        """
        from sympy import Matrix as Mtx_Sympy

        if (self.W==0):
            print 'Strain energy function was not defined!'
            return

        # The C_prime matrix is defined here to help calculate dC/dC_e
        C_prime=self.Fg.transpose()*self.C*self.Fg

        S_PK=matrix(SR, 3, 3, [0 for i in xrange(9)])

        S_PK_Sympy=Mtx_Sympy(3,3,[0 for i in xrange(9)])
        SigmaTMP=Mtx_Sympy(3,3,[0 for i in xrange(9)])

        print 'Step0'
        sys.stdout.flush()

        # Substitute C=F^T*F
        self.CC=self.F.transpose()*self.F

        for i in xrange(3):
            for j in xrange(3):
                S_PK[i,j]=0
                S_PK_Sympy[i,j]=0

        for k in xrange(3):
            print 'k',k
            sys.stdout.flush()
            start = time.time()

            for l in xrange(3):
                comp=self.W.diff(self.C[k,l])*2
                comp_expd=(comp.substitute([self.C.list()[ni]==self.CC.list()[ni] for ni in xrange(9)]))._sympy_()
                #(self.substitute_components(comp, self.C, self.CC))._sympy_()
                for i in xrange(3):
                    for j in xrange(3):
                        S_PK[i,j]+=comp*C_prime[k,l].diff(self.C[i,j])
                        SigmaTMP[i,j]+=comp_expd*((C_prime[k,l].diff(self.C[i,j])).
                                                  substitute([self.C.list()[ni]==self.CC.list()[ni] for ni in xrange(9)]))._sympy_()
            end = time.time()
            print(end - start)
            sys.stdout.flush()

        S_PK_Sympy=SigmaTMP

        print 'Step1'
        sys.stdout.flush()

        self.S_PK_span=S_PK.list()

        # Form the 2nd Piola-Kirchoff stress tensor
        self.S_PK=matrix(SR, 3, S_PK.list())

        # Push forward the 2nd PK stress tensor to obtain the Cauchy stress tensor
        # sigma = Fe * S_PK * Fe^T / J_e
        self.Sigma=(self.Fe)*self.S_PK*transpose(self.Fe)*self.Jacobian_e**(-1)

        Fe_Sympy=Mtx_Sympy(3,3,self.Fe.list())

        SigmaTMP=Fe_Sympy*S_PK_Sympy*Fe_Sympy.T*(
            ((self.Jacobian_e.substitute([self.C.list()[ni]==self.CC.list()[ni] for ni in xrange(9)]))**(-1))._sympy_())

        print type(SigmaTMP)
        sys.stdout.flush()

        #(self.Fe)*SigmaTMP*transpose(self.Fe)*self.Jacobian_e**(-1)
        print 'Step2', type(SigmaTMP)
        sys.stdout.flush()

        # Remove the redudunt stress terms and store in FEA specific format
        # Could be Voigt format or LSDyna format

        self.Sigma_FEA=self.tensor_2_to_FEA_Sympy(SigmaTMP)
        #self.tensor_to_FEA(Mtx_Sympy(SigmaTMP))
        self.CauchyStress=True
        print 'Step3'
        sys.stdout.flush()
        return

    def calc_cauchy_stress_noshear(self):
        r"""
        This function calculates the Cauchy stress tensor from the strain energy function
        """
        from sympy import Matrix as Mtx_Sympy

        if (self.W==0):
            print 'Strain energy function was not defined!'
            return

        S_PK=jacobian(self.W, self.C.list())*2

        #print S_PK
        self.S_PK_span=S_PK
        # Form the 2nd Piola-Kirchoff stress tensor
        self.S_PK=matrix(SR, 3, [S_PK[0,0], 0, 0, 0, S_PK[0,4], 0, 0, 0, S_PK[0,8]])


        # Push forward the 2nd PK stress tensor to obtain the Cauchy stress tensor
        self.Sigma=(self.F)*self.S_PK*transpose(self.F)*self.Jacobian**(-1)

        # Substitute C=F^T*F
        self.CC=self.F.transpose()*self.F

        SigmaTMP=copy(self.Sigma)
        #matrix(SR, 3, 3, [0 for i in xrange(9)])
        for ni in xrange(3):
            for nj in xrange(3):
                #SigmaTMP[ni,nj]=self.Sigma[ni,nj]
        		SigmaTMP[ni,nj]=SigmaTMP[ni,nj].substitute([self.C.list()[i]==self.CC.list()[i] for i in xrange(9)])

        # Remove the redudunt stress terms and store in FEA specific format
        # Could be Voigt format or LSDyna format
        self.Sigma_FEA=self.tensor_2_to_FEA(SigmaTMP)
        self.CauchyStress=True
        return

    def calc_cauchy_stress_visc(self):
        from sympy import Matrix as Mtx_Sympy

        if (self.W_visc==0):
            print 'No Viscous strain energy function defined!'
            return

        S_PK_visc=jacobian(self.W_visc, self.dC.list())*2

        #print S_PK
        self.S_PK_visc_span=S_PK_visc
        # Form the 2nd Piola-Kirchoff stress tensor
        self.S_PK_visc=matrix(SR, 3, [S_PK_visc[0,i] for i in xrange(9)])


        # Push forward the 2nd PK stress tensor to obtain the Cauchy stress tensor
        self.Sigma_visc=(self.F)*self.S_PK_visc*transpose(self.F)*self.Jacobian**(-1)

        # Substitute C=F^T*F
        self.CC=self.F.transpose()*self.F

        SigmaTMP_visc=copy(self.Sigma_visc)
        #matrix(SR, 3, 3, [0 for i in xrange(9)])
        for ni in xrange(3):
            for nj in xrange(3):
                SigmaTMP_visc[ni,nj]=SigmaTMP_visc[ni,nj].substitute([self.C.list()[i]==self.CC.list()[i] for i in xrange(9)])


        # Remove the redudunt stress terms and store in FEA specific format
        # Could be Voigt format or LSDyna format
        self.Sigma_FEA_visc=self.tensor_2_to_FEA((SigmaTMP_visc))
        self.CauchyStress_visc=True
        return

    def tensor_2_to_FEA(self, inMtx):
        r"""
        Convert from a tensor format (xx, xy, xz, yx, yy, yz, zx, zy, zz) to FEA stress component format
        The exact format is determined by the input variable FEAFormat to the class
        """
        from sympy import Matrix as Mtx_Sympy
        outMtx=Mtx_Sympy(6,1,[0 for i in xrange(6)])
        tmp=inMtx.list()
        for ni in xrange(6):
            print 'NI',ni
            sys.stdout.flush()
            outMtx[ni]=(tmp)[self.OutputIdx[ni]]
        return outMtx

    def tensor_2_to_FEA_Sympy(self, inMtx):
        from sympy import Matrix as Mtx_Sympy
        outMtx=Mtx_Sympy(6,1,[0 for i in xrange(6)])
        tmp=inMtx.reshape(9,1)
        for ni in xrange(6):
            print 'NI_Sym',ni
            sys.stdout.flush()
            outMtx[ni]=(tmp)[self.OutputIdx[ni],0]
        return outMtx


    def tensor_4_to_FEA(self, inMtx_4):
        r"""
        Convert from the 4th order tensor (9X9) format to (6x6) FEA format, where each dimension index is
        described as in the list StressFormat_[FEAFormat] """

        from sympy import Matrix as Mtx_Sympy
        return Mtx_Sympy(6,6,[inMtx_4[ni,nj] for ni in self.OutputIdx for nj in self.OutputIdx])

    def tensor_4_to_FEA_Sympy(self, inMtx_4):
        r"""
        Convert from the 4th order tensor (9X9) format to (6x6) FEA format, where each dimension index is
        described as in the list StressFormat_[FEAFormat] """

        from sympy import Matrix as Mtx_Sympy
        return Mtx_Sympy(6,6,[inMtx_4[ni,nj] for ni in self.OutputIdx for nj in self.OutputIdx])
    
    def tangent_matrix(self):
        r"""
        This function creates Tangent matrix as described in
        https://en.wikiversity.org/wiki/Nonlinear_finite_elements/Rate_form_of_hyperelastic_laws

        The matrix is stored in the FEA specific notation
        """
        from sympy import Matrix as Mtx_Sympy
        import sys
        if(self.CauchyStress):
            S_PK=self.S_PK.list()
            F=self.F

            for ni in xrange(9):
                # Calculates the 2nd order derivative \partial^2 W/\partial C_KL \partial C_MN
                jjj=(jacobian(S_PK[ni], self.C.list())+jacobian(S_PK[ni], self.C.T.list()))

                for nj in xrange(9):
                    jjj[0,nj]=jjj[0,nj].substitute([self.C.list()[i]==self.CC.list()[i] for i in xrange(9)])
                #jjj=Mtx_Sympy(jjj)
                if ni == 0:
                    outM=copy(jjj)
                else:
                    outM=outM.stack(jjj)
            # Convert from material elasticity to spatial elasticity tensor

            tangM=Mtx_Sympy(9,9,[0 for i in xrange(81)])
            for NI in xrange(9):
                print 'Tang', NI
                for NJ in xrange(9):
                    print NJ
                    sys.stdout.flush()
                    tmp=outM[NI,NJ]._sympy_()
                    for ni in xrange(9):
                        for nj in xrange(9):
                            i,j=myindex(Tensor[ni])
                            k,l=myindex(Tensor[nj])

                            K,L=myindex(Tensor[NI])
                            M,N=myindex(Tensor[NJ])
                            tangM[ni, nj]+=(F[i,K]*F[j,L]*F[k,M]*F[l,N])._sympy_()*tmp*(1/self.Jacobian.substitute(
                                    [self.C.list()[i]==self.CC.list()[i] for i in xrange(9)])._sympy_())
            # Do tensor rotation with regard to self.Z
            if (self.Z !=0):
                print ('Rotate 4th order tensor')
                tangM_Z=Mtx_Sympy(9,9,[0 for i in xrange(81)])
                Z=self.Z
                for NI in xrange(9):
                    for NJ in xrange(9):
                        tmp=tangM[NI,NJ]
                        for ni in xrange(9):
                            for nj in xrange(9):
                                i,j=myindex(Tensor[ni])
                                k,l=myindex(Tensor[nj])

                                K,L=myindex(Tensor[NI])
                                M,N=myindex(Tensor[NJ])
                                tangM_Z[ni, nj]+=(Z[i,K]*Z[j,L]*Z[k,M]*Z[l,N])._sympy_()*tmp

                tangM=tangM_Z

        print 'new test'
        #outM=(jacobian(self.Sigma.list(), self.C.list())*2).simplify_full()
        
        if (self.ElasticityTensor=='Spatial'):
            # Spatial here means the deformed position
            self.Spatial_FEA=self.tensor_4_to_FEA_Sympy(tangM)
        else:
            # Material means the reference position
            self.Material_FEA=self.tensor_4_to_FEA(outM)
        print 'conver'

        return

    def write(self):
        r"""
        Calculate stress tensor and elasticity tensor and write subroutines
        """
        from codegen import codegen as cg_local
        outroutine=self.outroutine
        outfile=self.outfile
        to_files=True
        project=self.project

        if not (self.CauchyStress):
            if (self.ModelingGrowth):
                self.calc_cauchy_stress_growth()
            else:
                self.calc_cauchy_stress()
            if (self.Viscoelastic):
                self.calc_cauchy_stress_visc()
                print 'Visc'

        if (self.verbose):
            print 'Writing code for Cauchy stress tensor'
            sys.stdout.flush()
            
        result=cg_local([(outroutine, self.Sigma_FEA)], self.lang, outfile, project, to_files)
        if (self.Viscoelastic):
            result=cg_local((outroutine+'Visc', self.Sigma_FEA_visc), self.lang, outfile+'Visc', project, to_files)

        if (self.Imp):
#            if (self.ModelingGrowth):
#                raise ValueError("Implicit for growth modeling is not implemented!")
#                return 0
            
            self.tangent_matrix()

            outroutineimp=outroutine+"Imp"
            outfileimp=outfile+"Imp"
            if (self.ElasticityTensor=='Spatial'):
                result_imp=cg_local([(outroutineimp, self.Spatial_FEA)], self.lang, outfileimp, project, to_files)
            else:
                result_imp=cg_local([(outroutineimp, self.Material_FEA)], self.lang, outfileimp, project, to_files)
        return result

function IsTrace0(N,p,f)
    /* Checks if the trace of the modular form from the space M_2(Gamma0(Np)) to M_2(Gamma0(p)) vanishes  */
    /* This is equivalent to f being a newform on M_2(Gamma0(Np)) */
    R := Parent(Coefficient(f,0));
    M := ModularForms(Gamma0(N*p));
    MR := BaseExtend(M,R);
    return IsNewform(MR!f);
end function;
    

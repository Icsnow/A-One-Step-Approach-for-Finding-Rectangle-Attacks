
/*
This code for Eurocrypt accepted paper "A One-Step Approach for Finding Rectangle Attacks"
*/

array[0..15] of var 0..15: SP = array1d(0..15, [0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11]); % permutation of shiftrow


/*====================================================================================================
                                             Distinguisher
====================================================================================================*/
int: Eb = 1;
int: Ed = 10;
int: Ef = 3;
constraint assert((Eb >= 1) /\ (Ed >=1) /\ (Ef >= 1), "Rounds out of bounds");

% key difference from distinguisher.
array[0..Eb-1, 0..15] of var 0..1: DK_Eb = array2d(0..Eb-1, 0..15, [0,0,0,1, 0,0,0,0, 1,0,1,0, 0,0,0,0]);
array[Eb+Ed..Eb+Ed+Ef, 0..15] of var 0..1: DK_Ef = array2d(Eb+Ed..Eb+Ed+Ef, 0..15, [0,0,1,0, 0,0,0,1, 1,0,0,0, 0,0,0,0,
                                                                                         0,0,0,0, 0,0,0,0, 0,0,0,0, 0,1,1,1,
                                                                                         0,0,0,0, 0,0,1,0, 0,1,0,0, 1,0,0,0,
                                                                                         0,1,0,1, 0,0,0,0, 1,0,0,0, 0,0,0,0]);
% Difference of Z_0
constraint forall(i in [5,6,7,8,9,10,11,12,14,15])((DZ_Eb[Eb-1,i] = 1) /\ (dz_Eb[Eb-1,i] = 0))
           /\ sum(i in 0..15)(DZ_Eb[Eb-1,i] + dz_Eb[Eb-1,i]) = 10;
% Difference of X_11
constraint forall(i in 0..15) ((DX_Ef[Eb+Ed,i] + dx_Ef[Eb+Ed,i] = 0));


/*====================================================================================================
                              Differential Propagation in Extended Rounds
====================================================================================================*/

/*##################################################################
  PARAMETERS:   
   X(x): State before Add Round Tweakey
   Y(y): State before SBox
   Z(z): State before ShiftRow
   S(s): State before MixColumn
   W(w): State after MixColumn
   WSB: Weight consumption of SBox
   WMC: Weight consumption of MixColumn
   FSB: Filter in SBox
   FMC: Filter in MixColumn
###################################################################*/

/*
   D(non-zreo=1,zero=0) d(unknow diff=1,known=1)
   0                    0                        diff ==> 0
   1                    0                        diff ==> fixed
   1                    1                        diff ==> truncated
*/

array[0..Eb-1, 0..15] of var 0..1: DX_Eb;
array[0..Eb-1, 0..15] of var 0..1: dx_Eb;
array[0..Eb-1, 0..15] of var 0..1: DY_Eb;
array[0..Eb-1, 0..15] of var 0..1: dy_Eb;
array[0..Eb-1, 0..15] of var 0..1: DZ_Eb;
array[0..Eb-1, 0..15] of var 0..1: dz_Eb;
array[0..Eb-1, 0..15] of var 0..1: DS_Eb;
array[0..Eb-1, 0..15] of var 0..1: ds_Eb;
array[0..Eb-1, 0..15] of var 0..1: DW_Eb;
array[0..Eb-1, 0..15] of var 0..1: dw_Eb;
array[0..Eb-1, 0..15] of var 0..1: WSB_Eb;
array[0..Eb-1, 0..3] of var 0..3: WMC_Eb;

array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: DX_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: dx_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: DY_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: dy_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: DZ_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: dz_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: DS_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: ds_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: DW_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: dw_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: WSB_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..3] of var 0..3: WMC_Ef;

/*****************
 Add Round Tweakey
*****************/
constraint 
  forall(r in 0..Eb-1, i in 0..15)(
    D_ATK(DY_Eb[r,i], dy_Eb[r,i], DK_Eb[r,i], DX_Eb[r,i], dx_Eb[r,i]) 
  )
  /\
  forall(r in Eb+Ed..Eb+Ed+Ef-1, i in 0..15)(
    D_ATK(DX_Ef[r,i], dx_Ef[r,i], DK_Ef[r,i], DY_Ef[r,i], dy_Ef[r,i]) 
  )
;

/*****************
      Sbox
*****************/
constraint 
  forall(r in 0..Eb-1, i in 0..15)(
    D_SB(DS_Eb[r,i], ds_Eb[r,i], DY_Eb[r,i], dy_Eb[r,i], WSB_Eb[r,i]) 
  )
  /\
  forall(r in Eb+Ed..Eb+Ed+Ef-1, i in 0..15)(
    D_SB(DY_Ef[r,i], dy_Ef[r,i], DS_Ef[r,i], ds_Ef[r,i], WSB_Ef[r,i]) 
  )
;

/*****************
    ShiftRow
*****************/
constraint
  forall(r in 0..Eb-1, i in 0..15)(
    (DS_Eb[r,SP[i]] = DZ_Eb[r,i]) /\ (ds_Eb[r,SP[i]] = dz_Eb[r,i]) 
  )
  /\
  forall(r in Eb+Ed..Eb+Ed+Ef-1, i in 0..15)(
    (DS_Ef[r,SP[i]] = DZ_Ef[r,i]) /\ (ds_Ef[r,SP[i]] = dz_Ef[r,i]) 
  )
;

/****************
    MixColumn
****************/
constraint
  forall(r in 0..Eb-1, i in 0..3)(
    D_MC(DW_Eb[r,4*i], DW_Eb[r,(4*i+1)], DW_Eb[r,(4*i+2)], DW_Eb[r,(4*i+3)],
         dw_Eb[r,4*i], dw_Eb[r,(4*i+1)], dw_Eb[r,(4*i+2)], dw_Eb[r,(4*i+3)],
         DZ_Eb[r,4*i], DZ_Eb[r,(4*i+1)], DZ_Eb[r,(4*i+2)], DZ_Eb[r,(4*i+3)],
         dz_Eb[r,4*i], dz_Eb[r,(4*i+1)], dz_Eb[r,(4*i+2)], dz_Eb[r,(4*i+3)],
         WMC_Eb[r,i])
  )
  /\
  forall(r in Eb+Ed..Eb+Ed+Ef-1, i in 0..3)(
    D_MC(DZ_Ef[r,(4*i)], DZ_Ef[r,(4*i+1)], DZ_Ef[r,(4*i+2)], DZ_Ef[r,(4*i+3)],
         dz_Ef[r,(4*i)], dz_Ef[r,(4*i+1)], dz_Ef[r,(4*i+2)], dz_Ef[r,(4*i+3)],
         DW_Ef[r,(4*i)], DW_Ef[r,(4*i+1)], DW_Ef[r,(4*i+2)], DW_Ef[r,(4*i+3)],
         dw_Ef[r,(4*i)], dw_Ef[r,(4*i+1)], dw_Ef[r,(4*i+2)], dw_Ef[r,(4*i+3)],
         WMC_Ef[r,i]) 
  )
;

/****************
 Round Connection
****************/
constraint
  if (Eb >= 2) then(
    forall(r in 1..Eb-1, i in 0..15)(
      (DX_Eb[r,i] = DW_Eb[r-1,i])
      /\
      (dx_Eb[r,i] = dw_Eb[r-1,i]) 
    )
  )endif
  /\
  if (Ef >= 2) then(
    forall(r in Eb+Ed+1..Eb+Ed+Ef-1, i in 0..15)(
      (DX_Ef[r,i] = DW_Ef[r-1,i])
      /\
      (dx_Ef[r,i] = dw_Ef[r-1,i]) 
    )
  )endif
;

/*====================================================================================================
                                          Value Propagation
====================================================================================================*/

array[0..Eb-1, 0..15] of var 0..1: gk_Eb;
array[0..Eb-1, 0..15] of var 0..1: VY_Eb;
array[0..Eb-1, 0..15] of var 0..1: VS_Eb;
array[0..Eb-1, 0..15] of var 0..1: VZ_Eb;
array[0..Eb-1, 0..15] of var 0..1: VW_Eb;
array[0..Eb-1, 0..15] of var 0..1: FSB_Eb;
array[0..Eb-1, 0..3] of var 0..3: FMC_Eb;

array[Eb+Ed+1..Eb+Ed+Ef, 0..15] of var 0..1: gk_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: VY_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: VS_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: VZ_Ef;
array[Eb+Ed..Eb+Ed+Ef-2, 0..15] of var 0..1: VW_Ef;
array[Eb+Ed..Eb+Ed+Ef-1, 0..15] of var 0..1: FSB_Ef;
array[Eb+Ed..Eb+Ed+Ef-2, 0..3] of var 0..3: FMC_Ef;

% For known plaintext-ciphertext
constraint forall(i in 0..15) (VY_Eb[0,i] = 1);  
constraint forall(i in 0..15) (VZ_Ef[Eb+Ed+Ef-1,i] = 1);

/****************
Sbox substitution
****************/
constraint 
  forall(r in 0..Eb-1, i in 0..15)(
    V_SB(VY_Eb[r,i], VS_Eb[r,i], dy_Eb[r,i], ds_Eb[r,i], gk_Eb[r,i], FSB_Eb[r,i]) 
  )
  /\
  forall(r in Eb+Ed..Eb+Ed+Ef-1, i in 0..15)(
    V_SB(VS_Ef[r,i], VY_Ef[r,i], ds_Ef[r,i], dy_Ef[r,i], gk_Ef[r+1,i], FSB_Ef[r,i]) 
  )
;

/****************
    ShiftRow
****************/
constraint
  forall(r in 0..Eb-1, i in 0..15)(
    VZ_Eb[r,i] = VS_Eb[r,SP[i]]
  )
  /\
  forall(r in Eb+Ed..Eb+Ed+Ef-1, i in 0..15)(
    VZ_Ef[r,i] = VS_Ef[r,SP[i]]
  )
;

/****************
    MixColumn
****************/
constraint
  forall(r in 0..Eb-1, i in 0..3)(
    V_MC(VZ_Eb[r,4*i], VZ_Eb[r,4*i+1], VZ_Eb[r,4*i+2], VZ_Eb[r,4*i+3],
         VW_Eb[r,4*i], VW_Eb[r,4*i+1], VW_Eb[r,4*i+2], VW_Eb[r,4*i+3],
         dz_Eb[r,4*i], dz_Eb[r,4*i+1], dz_Eb[r,4*i+2], dz_Eb[r,4*i+3],
         dw_Eb[r,4*i], dw_Eb[r,4*i+1], dw_Eb[r,4*i+2], dw_Eb[r,4*i+3],
         FMC_Eb[r,i])
  )
  /\
  forall(r in Eb+Ed..Eb+Ed+Ef-2, i in 0..3)(
    V_MC(VW_Ef[r,4*i], VW_Ef[r,4*i+1], VW_Ef[r,4*i+2], VW_Ef[r,4*i+3],
         VZ_Ef[r,4*i], VZ_Ef[r,4*i+1], VZ_Ef[r,4*i+2], VZ_Ef[r,4*i+3],
         dw_Ef[r,4*i], dw_Ef[r,4*i+1], dw_Ef[r,4*i+2], dw_Ef[r,4*i+3],
         dz_Ef[r,4*i], dz_Ef[r,4*i+1], dz_Ef[r,4*i+2], dz_Ef[r,4*i+3],
         FMC_Ef[r,i])
  )
;

/****************
 Round Connection
****************/
constraint
  if (Eb >= 2) then(
    forall(r in 0..Eb-2, i in 0..15)(
    VW_Eb[r,i] = VY_Eb[r+1,i]
    )
  )endif
  /\
  if (Ef >= 2) then(
    forall(r in Eb+Ed+1..Eb+Ed+Ef-1, i in 0..15)(
      VW_Ef[r-1,i] = VY_Ef[r,i]
    )
  )endif
;

/*====================================================================================================
                                           Complexity
====================================================================================================*/
var int: s; % s = log_2(2^{s/2})
var float: Pd;
var float: D;
var float: DR;
var float: T1;
var float: T2;
var float: T3;
var float: T4;
var float: TR;
var int: h;

constraint Pd = 40.7;
constraint s = 1;

/****************
   Parameters
****************/
var int: mb_prime = sum(r in 0..Eb-1, i in 0..15)(gk_Eb[r,i]) * 8;
var int: mf_prime = sum(r in Eb+Ed+1..Eb+Ef+Ed, i in 0..15)(gk_Ef[r,i]) * 8;
var int: rb = sum(i in 0..15) (dy_Eb[0,i]) * 8;
var int: rf = sum(i in 0..15) (dz_Ef[Eb+Ed+Ef-1,i]) * 8;
var int: rb_prime = (sum(r in 0..Eb-1, i in 0..15)(FSB_Eb[r,i]) + sum(r in 0..Eb-1, i in 0..3)(FMC_Eb[r,i])) * 8;
var int: rf_prime = (sum(r in Eb+Ed..Eb+Ed+Ef-1, i in 0..15)(FSB_Ef[r,i]) + sum(r in Eb+Ed..Eb+Ed+Ef-2, i in 0..3)(FMC_Ef[r,i])) * 8;
var int: rb_star = rb - rb_prime;
var int: rf_star = rf - rf_prime;

/****************
   Complexity
****************/
constraint D = s + 64 + (sum(r in 0..Eb-1, c in 0..3) (WMC_Eb[r,c]) + 
                         sum(r in 0..Eb-1, i in 0..15) (WSB_Eb[r,i]) +
                         sum(r in Eb+Ed..Eb+Ed+Ef-1, c in 0..3)(WMC_Ef[r,c]) + 
                         sum(r in Eb+Ed..Eb+Ed+Ef-1, i in 0..15) (WSB_Ef[r,i])) * 8 + Pd;
constraint DR = 2 + D;

constraint T1 = mb_prime + mf_prime + DR;
constraint T2 = mb_prime + mf_prime + D + rb_star;
constraint T3 = mb_prime + mf_prime + 2 * (D + rb_star + rf_star - 128);
constraint T4 = 384 - h;

constraint (TR >= T1) /\ (TR >= T2) /\ (TR >= T3) /\ (TR >= T4);

constraint rb_star >= 0 /\ rf_star >= 0 /\ DR <= 128;

/*****************
Objective Function
*****************/
solve minimize TR;

/*====================================================================================================
                                             PREDICATES
====================================================================================================*/

predicate D_ATK(var 0..1: X,
              var 0..1: x,
              var 0..1: K,
              var 0..1: Y,
              var 0..1: y) = 
  (-X + K + Y >= 0)
  /\
  (X - K + Y >= 0)
  /\
  (X + K - Y >= 0)
  /\
  (x = y)
  /\
  (Y >= y)
;

predicate D_SB(var 0..1: X,
             var 0..1: x,
             var 0..1: Y,
             var 0..1: y,
             var 0..1: w) = 
  (X >= x) 
  /\ 
  (X >= Y)
  /\ 
  (X = Y)
  /\
  (w = Y - y)
;

predicate D_MC(var 0..1: X0, var 0..1: X1, var 0..1: X2, var 0..1: X3, 
               var 0..1: x0, var 0..1: x1, var 0..1: x2, var 0..1: x3,
               var 0..1: Y0, var 0..1: Y1, var 0..1: Y2, var 0..1: Y3, 
               var 0..1: y0, var 0..1: y1, var 0..1: y2, var 0..1: y3,
               var 0..3: w) = 
  if(X0 + X1 + X2 + X3 >= 1) /\ (x0 + x1 + x2 + x3 >=1) then(
    (X0 + X1 + X2 + X3 + Y0 + Y1 + Y2 + Y3 >= 5)
    /\
    (X0 + X1 + X2 + X3 + Y0 + Y1 + Y2 + Y3 <= 8)
    /\
    (x0 + x1 + x2 + x3 + y0 + y1 + y2 + y3 >= 5)
    /\
    (x0 + x1 + x2 + x3 + y0 + y1 + y2 + y3 <= 8)
    /\
    (w = 4 - y0 - y1 - y2 - y3)
  )
  elseif(X0 + X1 + X2 + X3 >= 1) then(
    (X0 + X1 + X2 + X3 + Y0 + Y1 + Y2 + Y3 >= 5)
    /\
    (X0 + X1 + X2 + X3 + Y0 + Y1 + Y2 + Y3 <= 8)
    /\
    (x0 + x1 + x2 + x3 + y0 + y1 + y2 + y3 = 0)
    /\
    (w = 0)
  )
  else(
    (X0 + X1 + X2 + X3 + Y0 + Y1 + Y2 + Y3 = 0)
    /\
    (x0 + x1 + x2 + x3 + y0 + y1 + y2 + y3 = 0)
    /\
    (w = 0)
  )
  endif
;

predicate V_SB(var 0..1: vin,
               var 0..1: vout,
               var 0..1: din,
               var 0..1: dout,
               var 0..1: gk,
               var 0..1: filter) = 
  if (vin == 1) /\ (gk == 1) then(
    (vout = 1)
    /\
    (filter = din - dout)
  )
  else(
    (vout = 0)
    /\
    (filter = 0)
  )
  endif
;

predicate V_MC(var 0..1: vin0,  var 0..1: vin1,  var 0..1: vin2,  var 0..1: vin3,
               var 0..1: vout0, var 0..1: vout1, var 0..1: vout2, var 0..1: vout3,
               var 0..1: din0,  var 0..1: din1,  var 0..1: din2,  var 0..1: din3,
               var 0..1: dout0, var 0..1: dout1, var 0..1: dout2, var 0..1: dout3,
               var 0..3: filter) = 
  if(vin0 + vin1 + vin2 + vin3 == 4) then(
    (vout0 + vout1 + vout2 + vout3 = 4)
    /\
    (filter = (din0 + din1 + din2 + din3) - (dout0 + dout1 + dout2 + dout3))
  )
  else(
    (vout0 + vout1 + vout2 + vout3 = 0)
    /\
    (filter = 0)
  )
  endif
;
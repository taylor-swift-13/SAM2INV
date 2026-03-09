int main1(int d,int u){
  int mhs0, ln7x, hf, x1t, oo, nej;
  mhs0=u+24;
  ln7x=0;
  hf=0;
  x1t=5;
  oo=0;
  nej=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mhs0 == \at(u, Pre) + 24;
  loop invariant u - 2*hf == \at(u, Pre);
  loop invariant (ln7x == 0) || (ln7x == mhs0);
  loop invariant oo == (hf * (hf + 1)) / 2;
  loop invariant ln7x >= 0;
  loop invariant (oo == hf);
  loop invariant (x1t == 5 + hf);
  loop invariant (0 <= hf && hf <= 1);
  loop invariant ((ln7x == 0) ==> (hf == 0));
  loop invariant ((ln7x == 0) ==> (oo == 0));
  loop invariant ((ln7x == 0) ==> (u == \at(u, Pre)));
  loop invariant ((ln7x == 0) ==> (x1t == 5));
  loop invariant ((ln7x == 0) ==> (nej == -5));
  loop invariant ((ln7x == mhs0) ==> (nej == mhs0 - 5));
  loop assigns hf, u, nej, oo, x1t, ln7x;
*/
while (ln7x<mhs0) {
      hf += 1;
      u += 2;
      nej = nej+mhs0-ln7x;
      oo += hf;
      x1t += hf;
      ln7x = mhs0;
  }
}
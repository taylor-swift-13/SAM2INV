int main1(){
  int nh, vf, v6, g, mz;
  nh=1;
  vf=0;
  v6=-6;
  g=nh;
  mz=nh;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= vf;
  loop invariant vf <= nh;
  loop invariant nh == 1;
  loop invariant (g == nh + 2*v6 + 12);
  loop invariant v6 <= -6;
  loop invariant (1 - 4*vf <= mz);
  loop invariant (mz <= 1 + 4*vf);
  loop invariant v6 % 2 == 0;
  loop assigns mz, vf, v6, g;
*/
while (vf < nh) {
      mz = mz+(v6%5);
      vf++;
      v6 = v6*2;
      g += v6;
  }
}
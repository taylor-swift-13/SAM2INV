int main1(){
  int hs, fa, u0e, zw5, qlj9, tk2, i8jh;
  hs=52;
  fa=-4;
  u0e=8;
  zw5=hs;
  qlj9=(1%6)+2;
  tk2=25;
  i8jh=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zw5 == hs;
  loop invariant u0e > 0;
  loop invariant u0e % 8 == 0;
  loop invariant fa <= -4;
  loop invariant i8jh <= 3;
  loop invariant tk2 >= 25;
  loop invariant qlj9 == 3;
  loop invariant hs == 52;
  loop assigns u0e, fa, tk2, i8jh, zw5;
*/
while (zw5<hs) {
      u0e = u0e*qlj9;
      fa = fa*qlj9+1;
      tk2 = tk2*2+(u0e%5)+3;
      i8jh = i8jh + fa;
      zw5 = hs;
  }
}
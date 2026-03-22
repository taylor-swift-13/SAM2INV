int main1(){
  int s5, z, ktb, v5, sx;
  s5=1;
  z=(1%28)+8;
  ktb=(1%22)+5;
  v5=0;
  sx=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z % 9 == 0;
  loop invariant v5 >= 0;
  loop invariant s5 == 1;
  loop invariant (v5 + ktb * z) == 54;
  loop invariant 0 <= ktb;
  loop invariant ktb <= 6;
  loop invariant z >= 9;
  loop invariant sx == z/3 - 3;
  loop assigns v5, ktb, z, sx;
*/
while (ktb!=0) {
      if (ktb%2==1) {
          v5 += z;
          ktb--;
      }
      ktb = ktb/2;
      z = 2*z;
      sx = sx*2+(z%2)+2;
      sx += s5;
  }
}
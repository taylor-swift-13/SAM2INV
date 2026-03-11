int main1(int o){
  int qsq5, z, b, su3m, puvk;
  qsq5=o*3;
  z=0;
  b=0;
  su3m=0;
  puvk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant puvk == z;
  loop invariant su3m < 6;
  loop invariant 0 <= z;
  loop invariant 0 <= b;
  loop invariant qsq5 == \at(o, Pre) * 3;
  loop invariant puvk == b * 6 + su3m;
  loop invariant su3m >= 0;
  loop assigns z, puvk, su3m, b;
*/
for (; z<qsq5; z += 1) {
      puvk++;
      su3m += 1;
      if (su3m>=6) {
          su3m -= 6;
          b += 1;
      }
  }
}
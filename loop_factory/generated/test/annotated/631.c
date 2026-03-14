int main1(int o){
  int b4, v, q8, en, ma, z;
  b4=o;
  v=0;
  q8=38;
  en=0;
  ma=1;
  z=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant en + q8 == 38;
  loop invariant en >= 0;
  loop invariant q8 >= 0;
  loop invariant z >= 0;
  loop invariant v >= 0;
  loop invariant ma == v + 1;
  loop invariant en <= (v * (v + 1)) / 2;
  loop assigns en, q8, v, ma, z;
*/
while (q8>0&&v<b4) {
      if (q8<=ma) {
          z = q8;
      }
      else {
          z = ma;
      }
      v++;
      ma += 1;
      en += z;
      q8 -= z;
  }
}
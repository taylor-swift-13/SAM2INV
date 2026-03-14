int main1(int f,int e){
  int s, jk0, uq, sr, rs;
  s=e+17;
  jk0=0;
  uq=0;
  sr=0;
  rs=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rs == jk0;
  loop invariant sr == jk0 % 10;
  loop invariant uq == jk0 / 10;
  loop invariant s == \at(e, Pre) + 17;
  loop invariant e == \at(e, Pre);
  loop invariant 0 <= sr;
  loop invariant sr <= 9;
  loop invariant 0 <= uq;
  loop assigns jk0, rs, sr, uq;
*/
while (jk0<s) {
      sr++;
      rs++;
      if (sr>=10) {
          sr = sr - 10;
          uq += 1;
      }
      jk0 = jk0 + 1;
  }
}
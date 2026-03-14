int main1(){
  int am, qk, xj, r8z;
  am=176;
  qk=am;
  xj=am;
  r8z=qk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xj == qk;
  loop invariant am == r8z;
  loop invariant qk >= am;
  loop invariant am == 176;
  loop assigns xj, qk;
*/
while (qk-6>=0) {
      if (qk<am/2) {
          xj += r8z;
      }
      else {
          xj++;
      }
      qk++;
  }
}
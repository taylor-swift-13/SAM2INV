int main1(){
  int jg, f1k2;
  jg=0;
  f1k2=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jg >= 0;
  loop invariant f1k2 == 9;
  loop assigns jg, f1k2;
*/
while (f1k2>0&&f1k2>0) {
      if (jg%2==0) {
          f1k2 = f1k2 - 1;
      }
      else {
          f1k2 = f1k2 - 1;
      }
      jg += 1;
      f1k2 += 1;
  }
}
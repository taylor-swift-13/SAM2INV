int main1(){
  int fc, ta, n;
  fc=0;
  ta=(1%20)+10;
  n=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ta;
  loop invariant 0 <= n;
  loop invariant (fc >= 0);
  loop invariant ta == 11 - ((fc + 1) / 2);
  loop invariant n == 9 - (fc / 2);
  loop assigns fc, ta, n;
*/
while (ta>0&&n>0) {
      if (!(!(fc%2==0))) {
          ta--;
      }
      else {
          n = n - 1;
      }
      fc = fc + 1;
  }
}
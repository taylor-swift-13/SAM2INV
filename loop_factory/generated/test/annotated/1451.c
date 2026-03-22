int main1(){
  int rwf0, uha, va, b;
  rwf0=9;
  uha=0;
  va=0;
  b=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uha + b == 8;
  loop invariant va == 8 * uha - (uha * (uha - 1)) / 2;
  loop invariant b + uha == rwf0 - 1;
  loop assigns uha, va, b;
*/
while (1) {
      if (!(uha<rwf0&&b>0)) {
          break;
      }
      uha = uha + 1;
      va += b;
      b = b - 1;
  }
}
int main1(int n){
  int zlv, q;
  zlv=1;
  q=zlv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre);
  loop invariant zlv == 1;
  loop invariant q == 0 || q == 1;
  loop assigns n, q;
*/
while (q!=q) {
      if (q>q) {
          q = q - q;
          q = q + q;
      }
      else {
          q = q - q;
          q = q + q;
      }
      n = n+q-q;
  }
}
int main1(){
  int s, we29, k;
  s=1+23;
  we29=s;
  k=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((we29 == s) && (k == 1)) || ((we29 == 0) && (k == 2));
  loop invariant (s == 1 + 23);
  loop assigns k, we29;
*/
while (we29>=1) {
      if (k==1) {
          k = 2;
      }
      else {
          if (k==2) {
              k = 1;
          }
      }
      we29 = 0;
  }
}
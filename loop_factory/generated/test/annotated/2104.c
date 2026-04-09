int main1(){
  int cqq, k, h, bn;
  cqq=1;
  k=0;
  h=k;
  bn=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bn + h == 12;
  loop invariant h == k;
  loop invariant bn + k == 12;
  loop invariant cqq == 1;
  loop invariant (0 <= k && k <= cqq);
  loop assigns bn, k, h;
*/
while (k < cqq) {
      bn -= 1;
      k += 1;
      h += 1;
  }
}
int main1(int v){
  int i, of2n, lgnc, vk;
  i=v;
  of2n=0;
  lgnc=0;
  vk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= of2n;
  loop invariant v == i + ((of2n + 1) / 2);
  loop invariant lgnc == of2n % 2;
  loop invariant vk == of2n % 2;
  loop invariant i == \at(v, Pre);
  loop invariant (i >= 0) ==> (of2n <= i);
  loop assigns of2n, lgnc, vk, v;
*/
while (of2n < i) {
      of2n++;
      vk = 1 - vk;
      lgnc = 1 - lgnc;
      v += lgnc;
  }
}
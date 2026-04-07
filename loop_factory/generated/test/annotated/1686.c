int main1(int d){
  int k, i, s, nf01;
  k=59;
  i=0;
  s=i;
  nf01=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (i == 0) ==> (nf01 == -6);
  loop invariant k == 59;
  loop invariant (i == 0) || (i == k);
  loop invariant (i == k) ==> (s == d && nf01 == -6 + k);
  loop invariant (i == 0) ==> (s == 0);
  loop invariant (i != 0) ==> (nf01 == -6 + k);
  loop assigns s, nf01, i;
*/
while (1) {
      if (!(i < k)) {
          break;
      }
      s = s + d*(1 - 2*(i >= k/2));
      nf01 = nf01 + k;
      i = k;
  }
}
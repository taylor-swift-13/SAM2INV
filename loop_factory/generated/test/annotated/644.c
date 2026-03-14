int main1(){
  int y6, k, gvb, nv;
  y6=(1%33)+5;
  k=y6;
  gvb=8;
  nv=y6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (k % 2) == 0;
  loop invariant y6 == 1 % 33 + 5;
  loop invariant 0 <= k <= y6;
  loop assigns k;
*/
for (; k-2>=0; k -= 2) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nv == 1 % 33 + 5;
  loop invariant y6 == 1 % 33 + 5;
  loop invariant k <= nv;
  loop invariant 0 <= k;
  loop invariant gvb >= 0;
  loop assigns k, gvb;
*/
while (k<nv) {
      k += 1;
      gvb = nv-k;
      gvb = gvb - gvb;
  }
}
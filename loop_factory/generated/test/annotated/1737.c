int main1(int q){
  int l2p, k, nh;
  l2p=5;
  k=0;
  nh=l2p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (nh + 1) % (l2p + 1) == 0;
  loop invariant 0 <= k <= l2p;
  loop invariant nh % 2 == 1;
  loop assigns nh, k;
*/
while (k < l2p) {
      nh += nh;
      k += 1;
      nh++;
  }
}
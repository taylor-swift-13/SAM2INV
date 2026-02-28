int main1(int n,int q){
  int w, k, v;

  w=45;
  k=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 0;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant k <= w;
  loop invariant k >= 0;
  loop invariant w == 45;
  loop invariant 0 <= k <= w;
  loop invariant 0 <= k;
  loop assigns k, v;
*/
while (k<=w-1) {
      if (v<w+2) {
          v = v+v;
      }
      else {
          v = v-v;
      }
      k = k+1;
  }

}

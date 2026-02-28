int main1(int k,int q){
  int b, n, w, v;

  b=k;
  n=0;
  w=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == k;

  loop invariant (w < b/2) ==> (v == k);

  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant w >= 0;
  loop invariant v >= k;
  loop invariant (v - k) % 2 == 0;
  loop invariant (w < b/2) ==> (v == \at(k, Pre));

  loop invariant (q == \at(q, Pre));
  loop invariant ((v - k) % 2 == 0);
  loop assigns v, w;
*/
while (w<b) {
      if (w>=b/2) {
          v = v+2;
      }
      w = w+1;
  }

}

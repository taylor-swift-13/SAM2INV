int main1(int m){
  int p, w, v;

  p=25;
  w=0;
  v=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= w <= p;
  loop invariant p == 25;
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= w;
  loop invariant w <= p;
  loop assigns w;
*/
while (w<p) {
      w = w+1;
  }

}

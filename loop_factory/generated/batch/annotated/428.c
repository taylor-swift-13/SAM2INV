int main1(int p,int q){
  int k, i, v;

  k=34;
  i=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant k == 34;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i <= k;
  loop invariant (v - p) % 4 == 0;
  loop invariant ((v - p) % 4) == 0;
  loop invariant 0 <= i;
  loop assigns v;
*/
while (i<k) {
      v = v+4;
      v = v*5;
  }

}

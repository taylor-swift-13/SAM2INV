int main1(int k,int p){
  int l, j, i, v;

  l=p;
  j=0;
  i=j;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == (j*(j-1))/2;
  loop invariant v == 0;
  loop invariant j >= 0;
  loop invariant l == p;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant i == j*(j-1)/2;
  loop invariant i >= 0;
  loop invariant v >= 0;
  loop assigns i, j, v;
*/
while (1) {
      i = i+j;
      v = v*v;
      v = v+i*v;
      j = j+1;
  }

}

int main1(int a,int k,int p,int q){
  int l, i, v;

  l=60;
  i=l;
  v=0;

  /*>>> LOOP INVARIANT TO FILL<<<*/
    /*@
    loop invariant i >= 0;
    loop invariant i <= 60;
    loop invariant v == 0;
    loop invariant l == 60;
    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && p == \at(p, Pre) && q == \at(q, Pre);
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant 0 <= i && i <= 60;
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i <= l;
    loop assigns i, v;
  */
  while (i>0) {
      v = v+v;
      v = v-v;
      i = i-1;
  }

}
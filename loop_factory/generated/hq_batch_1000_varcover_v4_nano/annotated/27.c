int main1(int a,int k,int n){
  int l, i, v, w;

  l=k;
  i=0;
  v=l;
  w=l;

  
  /*@

    loop invariant l == \at(k, Pre);

    loop invariant i >= 0;

    loop invariant v == l + i;

    loop invariant w == l - i;

    loop invariant i <= l || l <= 0;

    loop assigns i, v, w;

  */
while (i<l) {
      v = v+1;
      w = w-1;
      i = i+1;
  }

}
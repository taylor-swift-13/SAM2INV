int main1(int m,int n,int q){
  int l, i, v, w;

  l=q;
  i=0;
  v=n;
  w=i;

  
  /*@

    loop invariant w == 0;

    loop invariant l == \at(q,Pre);

    loop invariant i >= 0;

    loop invariant i <= l || l <= 0;

    loop assigns i, w;

  */
while (i<l) {
      w = w+w;
      i = i+1;
  }

}
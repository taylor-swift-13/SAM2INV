int main1(int b,int k,int p){
  int l, i, v;

  l=22;
  i=0;
  v=b;

  
  /*@

    loop invariant v - 2*i == b;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant p == \at(p, Pre);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      v = v+1;
      i = i+1;
  }

}
int main1(int b,int p,int q){
  int l, i, v, m;

  l=48;
  i=l;
  v=l;
  m=p;

  
  /*@

    loop invariant v == l + 2*m*(l - i);

    loop invariant 0 <= i && i <= l;

    loop invariant m == \at(p, Pre);

    loop assigns v, i;

    loop variant i;

  */
while (i>0) {
      v = v+m+m;
      i = i-1;
  }

}
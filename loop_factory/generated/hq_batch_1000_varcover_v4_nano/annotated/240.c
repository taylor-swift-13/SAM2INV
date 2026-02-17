int main1(int a,int p,int q){
  int l, i, v, m, o;

  l=27;
  i=l;
  v=-4;
  m=i;
  o=a;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v == -4 + (l - i) * (m + o);

    loop invariant o == a;

    loop invariant m == l;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+m+o;
      i = i-1;
  }

}
int main1(int a,int k,int p){
  int l, i, v, s;

  l=66;
  i=0;
  v=i;
  s=l;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant v == i;

    loop invariant (i == 0) ==> (s == l);

    loop invariant (i > 0) ==> (s == p);

    loop invariant l == 66;

    loop assigns v, s, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      s = s-1;
      s = p;
      i = i+1;
  }

}
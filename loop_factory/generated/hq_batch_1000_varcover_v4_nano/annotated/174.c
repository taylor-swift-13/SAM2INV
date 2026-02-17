int main1(int a,int k,int p){
  int l, i, v, u, x;

  l=58;
  i=0;
  v=i;
  u=l;
  x=l;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant v == 0;

    loop invariant x == l;

    loop invariant u == l + l*i + 5 * ((i + 5) / 6);

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant p == \at(p, Pre);

    loop assigns u, x, i;

    loop variant l - i;

  */
  while (i<l) {
      u = u+x;
      x = x+v;
      if ((i%6)==0) {
          u = u+5;
      }
      i = i+1;
  }

}
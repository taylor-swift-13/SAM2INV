int main1(int a,int b,int q){
  int l, i, v, e, t;

  l=(b%14)+17;
  i=0;
  v=q;
  e=i;
  t=q;

  
  /*@

    loop invariant v == \at(q, Pre) + i*(e + t + 1);

    loop invariant e == 0;

    loop invariant t == \at(q, Pre);

    loop invariant 0 <= i && i <= l;

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+e+t;
      v = v+1;
      i = i+1;
  }

}
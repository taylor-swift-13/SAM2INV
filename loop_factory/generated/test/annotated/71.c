int main1(int a,int b,int m,int p){
  int l, i, v, o;

  l=59;
  i=0;
  v=-3;
  o=l;

  
  /*@

    loop invariant (a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && p == \at(p, Pre));

    loop invariant v == i - 3;

    loop invariant i <= l;

    loop invariant o >= 56;

    loop invariant i >= 0 && i <= l;

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && p == \at(p, Pre);

    loop invariant o == l + i*(i+1)/2 - 3*i;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i >= 0;

    loop invariant o >= 59 + (i*i - 7*i)/2;


    loop invariant p == \at(p, Pre) && a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre);

    loop invariant 0 <= i <= l;

    loop assigns v, o, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      o = o+v;
      if (o+6<l) {
          o = o+i;
      }
      i = i+1;
  }

}
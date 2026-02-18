int main1(int b,int k,int m,int p){
  int l, i, v, o;

  l=22;
  i=l;
  v=k;
  o=k;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= 22;

    loop invariant b == \at(b,Pre) && k == \at(k,Pre) && m == \at(m,Pre) && p == \at(p,Pre);

    loop invariant l == 22;

    loop invariant k == \at(k, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i <= l;

    loop invariant o == 2*v - k;

    loop invariant 0 <= i <= 22;

    loop assigns i, v, o;

    loop variant i;

  */
while (i>0) {
      v = v*2;
      o = o+v;
      i = i-1;
  }

}
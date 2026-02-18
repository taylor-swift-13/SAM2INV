int main1(int a,int b,int k,int m){
  int l, i, v, w;

  l=79;
  i=0;
  v=i;
  w=b;

  
  /*@

    loop invariant v == 0;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant l == 79;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant 0 <= i && i <= l;

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && k == \at(k, Pre) && m == \at(m, Pre);


    loop invariant 0 <= i <= l;

    loop invariant (i == 0) ==> (w == b);

    loop invariant (i > 0) ==> (w % 2 != 0);

    loop assigns w, i;

    loop variant l - i;

  */
  while (i<l) {
      w = w+w;
      w = w+v;
      if (v+3<l) {
          w = w+1;
      }
      i = i+1;
  }

}
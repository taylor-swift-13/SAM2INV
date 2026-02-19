int main1(int b,int m){
  int l, i, v;

  l=m;
  i=0;
  v=i;

  
  /*@

    loop invariant ( (i == 0) && (v == 0) ) || (v == i + 7);

    loop invariant l == m;

    loop invariant m == \at(m, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant 0 <= i;


    loop invariant v >= i;


    loop invariant l >= m;

    loop invariant ((l - m) % 4) == 0;

    loop invariant ((i == 0) && (v == 0)) || (v == i + 7);


    loop invariant l == \at(m, Pre);

    loop invariant (i == 0) ==> (v == 0);

    loop invariant (i >= 1) ==> (v == i + 7);


    loop invariant (l == m);

    loop invariant (m == \at(m, Pre));

    loop invariant (b == \at(b, Pre));


    loop invariant (i == 0 && v == 0) || v == i + 7;


    loop assigns v, i;

  */
  while (i<l) {
      v = v+1;
      v = i+8;
      i = i+1;
  }

  /*@

     loop invariant l >= m;
     loop invariant ((l - m) % 4) == 0;
     loop invariant v >= i;
     loop assigns l, v;
  */
  while (v<i) {
      l = l+4;
      v = v+4;
  }

}
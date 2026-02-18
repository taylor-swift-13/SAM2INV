int main1(int a,int b,int m,int n){
  int l, i, v;

  l=44;
  i=l;
  v=i;

  
  /*@

    loop invariant l == 44;

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant (i >= 40) ==> (v == 44);

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && n == \at(n, Pre);

    loop invariant i <= 44;

    loop invariant v % 8 == 4;

    loop invariant v >= 44;


    loop invariant 0 <= i && i <= 44;


    loop assigns v, i;

  */
while (i>0) {
      if ((i%8)==0) {
          v = v+i;
      }
      i = i-1;
  }

}
int main1(int a,int b,int m,int p){
  int l, i, v;

  l=(a%33)+15;
  i=0;
  v=a;

  
  /*@

    loop invariant 0 <= i;



    loop invariant l == (\at(a, Pre) % 33) + 15;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && p == \at(p, Pre);

    loop invariant l == \at(a, Pre) % 33 + 15;

    loop invariant i <= l || l <= 0;

    loop invariant l == (a % 33) + 15;

    loop invariant (i == 0) ==> (v == a);


    loop invariant a == \at(a,Pre) && b == \at(b,Pre) && m == \at(m,Pre) && p == \at(p,Pre);

    loop invariant l == (\at(a,Pre) % 33) + 15;


    loop invariant i >= 0;

    loop invariant l == ((\at(a, Pre) % 33) + 15);

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v*2;
      v = v%7;
      i = i+1;
  }

}
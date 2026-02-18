int main1(int a,int m,int p,int q){
  int l, i, v, h;

  l=(a%9)+15;
  i=0;
  v=a;
  h=i;

  
  /*@

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant l == (a % 9) + 15;

    loop invariant v == a;

    loop invariant a == \at(a, Pre);

    loop invariant h * v >= 0;

    loop invariant l == (\at(a, Pre) % 9) + 15;

    loop invariant i >= 0;


    loop invariant (v == 0) ==> (h == 0);

    loop assigns h, i;

  */
  while (i<l) {
      h = h+h;
      h = h+v;
      i = i+1;
  }

}
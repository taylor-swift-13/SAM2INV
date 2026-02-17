int main1(int a,int p,int q){
  int l, i, v, c;

  l=23;
  i=0;
  v=p;
  c=a;

  
  /*@

    loop invariant v == \at(p,Pre) + i;

    loop invariant c == \at(a,Pre) + i * \at(p,Pre) + i*(i-1)/2;

    loop invariant 0 <= i && i <= l;

    loop invariant p == \at(p,Pre) && a == \at(a,Pre);

    loop assigns i, v, c;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      c = c-1;
      c = c+v;
      i = i+1;
  }

}
int main1(int b,int q){
  int e, v, w, u;

  e=(b%33)+17;
  v=1;
  w=0;
  u=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant u >= 1 && (w == 0 ==> u % 2 == 1) && (w > 0 ==> u % 2 == 0);
  loop invariant b == \at(b, Pre) && q == \at(q, Pre) && u >= 2*w;
  loop invariant e == (\at(b, Pre) % 33) + 17 && q == \at(q, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant e == \at(b, Pre) % 33 + 17;

  loop invariant u >= 1;
  loop invariant (w == 0) <==> (u % 2 == 1);
  loop invariant u >= w + 1;
  loop invariant e == (\at(b, Pre) % 33 + 17);
  loop invariant (w == 0) <==> (u == 1);
  loop invariant (w == 0 && u == 1) || (w >= 1 && u % 2 == 0);

  loop invariant ((w==0 && u==1) || (w>=1 && u%2==0)) && q == \at(q, Pre);
  loop invariant b == \at(b, Pre) && q == \at(q, Pre);

  loop assigns u, w;
*/
while (w<e) {
      if (w>=e/2) {
          u = u+2;
      }
      w = w+1;
      u = u+u;
  }

}

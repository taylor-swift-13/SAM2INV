int main1(int u,int h){
  int cc, w3, ci, wtq, mn;
  cc=h+13;
  w3=1;
  ci=0;
  wtq=(u%28)+10;
  mn=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mn == \at(u,Pre) + 2*ci;
  loop invariant u == \at(u,Pre) + ci*(cc - w3);
  loop invariant wtq == (\at(u,Pre) % 28) + 10 - (ci*(ci-1))/2;
  loop invariant ci >= 0;
  loop invariant cc == h + 13;
  loop invariant w3 == 1;
  loop invariant wtq == \at(u,Pre) % 28 + 10 - (ci*(ci - 1))/2 &&
                   mn  == \at(u,Pre) + 2*ci &&
                   u   == \at(u,Pre) + (cc - w3) * ci &&
                   cc  == \at(h,Pre) + 13 &&
                   w3  == 1 &&
                   0 <= ci;
  loop assigns wtq, mn, ci, u;
*/
while (wtq>ci) {
      wtq -= ci;
      mn += 2;
      ci = ci + 1;
      u = u+cc-w3;
  }
}
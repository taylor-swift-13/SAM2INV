int main1(int s){
  int p, evdq, mi, btv, w;
  p=(s%15)+17;
  evdq=p;
  mi=s;
  btv=s;
  w=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == (\at(s, Pre) % 15 + 17);
  loop invariant evdq <= p;
  loop invariant evdq >= 0;
  loop invariant (p - evdq == 0) ==> btv == \at(s, Pre);
  loop invariant (p - evdq > 0 && \at(s, Pre) > (p - evdq)) ==> btv == \at(s, Pre) - (p - evdq);
  loop invariant (p - evdq > 0 && \at(s, Pre) <= (p - evdq)) ==> btv == 0;
  loop invariant (\at(s, Pre) > 0) ==> mi == \at(s, Pre) + 2 * (p - evdq);
  loop invariant (\at(s, Pre) <= 0 && (p - evdq) == 0) ==> mi == \at(s, Pre);
  loop invariant (\at(s, Pre) <= 0 && (p - evdq) > 0) ==> mi == 2 * (p - evdq) + 1;
  loop invariant w >= mi;
  loop assigns evdq, mi, btv, w;
*/
while (evdq > 0) {
      evdq = (mi = mi>0 ? mi-1 : 0, btv = btv>0 ? btv-1 : 0, w = w>0 ? w-1 : 0, evdq-1);
      mi = mi + 3;
      w += mi;
  }
}
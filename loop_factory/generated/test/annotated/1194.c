int main1(){
  int oxd, ij, mh, i3u, ba;
  oxd=(1%36)+6;
  ij=oxd;
  mh=oxd;
  i3u=0;
  ba=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ij;
  loop invariant 0 <= mh;
  loop invariant ij <= oxd;
  loop invariant mh <= oxd;
  loop invariant (ij % oxd == 0);
  loop invariant (mh % oxd == 0);
  loop invariant ij % 7 == 0;
  loop invariant mh % 7 == 0;
  loop invariant i3u % 2 == 0;
  loop invariant ba % 2 == 0;
  loop assigns ij, mh, i3u, ba;
*/
while (1) {
      if (!(ij!=mh)) {
          break;
      }
      if (ij>mh) {
          ij = ij - mh;
          ba = ba + i3u;
      }
      else {
          mh = mh - ij;
          i3u = i3u + ba;
      }
      i3u = i3u*2+4;
      ba = ba*i3u+4;
  }
}
int main1(int e,int u,int r){
  int q6vq, lod8, p7;
  q6vq=59;
  lod8=q6vq;
  p7=r;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p7 - r == lod8 - q6vq;
  loop invariant e - \at(e, Pre) == p7 - r;
  loop invariant p7 >= r;
  loop invariant u - \at(u, Pre) == (p7 - r) * r + ((p7 - r) * (p7 - r + 1)) / 2;
  loop invariant lod8 <= q6vq;
  loop invariant p7 - r == lod8 - 59;
  loop invariant e - (lod8 - 59) == \at(e, Pre);
  loop invariant lod8 == 59 + (e - \at(e, Pre));
  loop invariant e >= \at(e, Pre);
  loop invariant u == \at(u, Pre) + (e - \at(e, Pre)) * r + ((e - \at(e, Pre)) * ((e - \at(e, Pre)) + 1)) / 2;
  loop invariant e - \at(e,Pre) == lod8 - q6vq;
  loop invariant u - \at(u,Pre) == (e - \at(e,Pre)) * r + (e - \at(e,Pre)) * (e - \at(e,Pre) + 1) / 2;
  loop assigns p7, lod8, e, u;
*/
while (1) {
      if (!(lod8<q6vq)) {
          break;
      }
      p7 += 1;
      lod8 = lod8 + 1;
      e += 1;
      u = u + p7;
  }
}
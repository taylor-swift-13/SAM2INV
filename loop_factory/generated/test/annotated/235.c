int main1(int k){
  int vt, w, rp, o8, id, g4;
  vt=29;
  w=1;
  rp=vt;
  o8=0;
  id=vt;
  g4=vt;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (w == vt) || (w == 1 && rp == vt && o8 == 0 && id == vt);
  loop invariant 1 <= w;
  loop invariant w <= vt;
  loop invariant (w == vt ==> (o8 == vt && rp == 2*vt && id == vt + 1));
  loop invariant ((w==1 && o8==0 && rp==vt && id==vt) ||
                    (w==vt && o8==vt && rp==2*vt && id==vt+1));
  loop invariant k == \at(k, Pre);
  loop assigns o8, id, rp, w;
*/
while (w<vt) {
      o8 += rp;
      id = id + w;
      rp = rp + o8;
      w = vt;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (rp - k) == (58 - \at(k, Pre));
  loop invariant g4 >= 29;
  loop invariant (rp - k) == (2*vt - \at(k, Pre));
  loop invariant rp >= 2*vt;
  loop invariant w == vt;
  loop invariant g4 == vt;
  loop invariant k == \at(k, Pre);
  loop assigns w, rp, k, g4;
*/
while (1) {
      if (!(rp<=vt-1)) {
          break;
      }
      w = w + k;
      rp++;
      k += 1;
      g4 = g4 + w;
  }
}
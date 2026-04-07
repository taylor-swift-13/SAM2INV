int main1(int w){
  int q4l, zv, qs, i5, uf, r6;
  q4l=(w%13)+13;
  zv=0;
  qs=0;
  i5=-8;
  uf=zv;
  r6=q4l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q4l == (\at(w, Pre) % 13) + 13;
  loop invariant r6 == q4l + qs*(qs+1)/2;
  loop invariant uf == 4*qs;
  loop invariant (qs <= q4l/2) ==> (i5 == -8);
  loop invariant (qs >= q4l/2) ==> (i5 == -8 + 2*(qs - q4l/2));
  loop invariant 0 <= qs <= q4l;
  loop assigns i5, qs, uf, r6;
*/
while (qs<q4l) {
      if (!(!(qs>=q4l/2))) {
          i5 += 2;
      }
      qs = qs + 1;
      uf += 4;
      r6 += qs;
  }
}
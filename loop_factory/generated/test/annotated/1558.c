int main1(){
  int iii, ql, d, hq2, p, k, dw, fc;
  iii=1+7;
  ql=0;
  d=1;
  hq2=4;
  p=ql;
  k=ql;
  dw=1+3;
  fc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dw == 4 + 3*ql;
  loop invariant 0 <= ql <= iii;
  loop invariant k == ql * (ql + 1) / 2;
  loop invariant fc == k;
  loop assigns d, hq2, ql, fc, k, dw, p;
*/
while (ql < iii) {
      if (ql % 2 == 0) {
          d += p;
      }
      else {
          hq2 = hq2 + k;
      }
      ql += 1;
      if (ql+5<=ql+iii) {
          fc = fc + ql;
      }
      k = k + ql;
      dw = dw + 3;
      p = p + 5;
      if (dw+6<iii) {
          fc = k-fc;
      }
      else {
          p = dw-p;
      }
  }
}
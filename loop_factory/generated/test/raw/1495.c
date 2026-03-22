int main1(int k){
  int h0, did, nv, pb, s;

  h0=66;
  did=h0;
  nv=did;
  pb=did;
  s=1;

  while (nv<=h0) {
      pb = pb*nv;
      if (nv<h0) {
          s = s*nv;
      }
      nv = nv + 1;
      k += pb;
  }

}

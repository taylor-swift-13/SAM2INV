int main1(int q){
  int a, vq, fa, u0bu, oci;

  a=(q%37)+13;
  vq=0;
  fa=q;
  u0bu=q;
  oci=8;

  while (vq < a) {
      fa = fa+oci-oci;
      vq = vq + 1;
      q = fa+u0bu+oci;
  }

}

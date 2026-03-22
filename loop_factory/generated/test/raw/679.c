int main1(int d){
  int hc, q, iv, w;

  hc=d;
  q=(d%40)+2;
  iv=0;
  w=hc;

  while (q!=iv) {
      iv = q;
      q = (q+hc/q)/2;
      w = w+q-iv;
  }

}

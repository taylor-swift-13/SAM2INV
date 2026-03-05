int main1(){
  int kv1, m2k, r48;

  kv1=1+21;
  m2k=1;
  r48=1;

  while (m2k<kv1) {
      if (r48>=10) {
          r48 = -1;
      }
      if (r48<=2) {
          r48 = 1;
      }
      r48 += r48;
      m2k += 1;
      r48 -= r48;
  }

}

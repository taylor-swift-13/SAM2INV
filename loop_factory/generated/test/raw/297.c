int main1(int t,int m){
  int kf, s8, k8, r, de2, q;

  kf=46;
  s8=kf;
  k8=0;
  r=1;
  de2=s8;
  q=kf;

  while (1) {
      if (!(k8<=kf-1)) {
          break;
      }
      r = r + k8;
      k8++;
      de2 = de2 + k8;
  }

  while (de2<q) {
      k8 = q-de2;
      de2 += 1;
      t = t + s8;
  }

}

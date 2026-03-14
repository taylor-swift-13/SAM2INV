int main1(int n){
  int k3b6, h7, q, ur5m;

  k3b6=n;
  h7=0;
  q=0;
  ur5m=k3b6;

  while (q<k3b6) {
      h7 += n;
      q += 1;
      ur5m = ur5m+(h7%5);
      n += 2;
  }

  while (1) {
      if (!(k3b6<q)) {
          break;
      }
      ur5m = ur5m+h7*k3b6;
      h7 += k3b6;
      k3b6 = q;
  }

}

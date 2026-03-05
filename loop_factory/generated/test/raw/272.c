int main1(){
  int uz, hd, v, sa3;

  uz=1+20;
  hd=uz;
  v=hd;
  sa3=uz;

  while (hd-2>=0) {
      if (hd<uz/2) {
          v = v + sa3;
      }
      else {
          v++;
      }
      sa3 += v;
  }

}

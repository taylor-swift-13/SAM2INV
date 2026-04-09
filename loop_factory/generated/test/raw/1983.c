int main1(int q){
  int vqss, ynmp, fu, itd2, m6;

  vqss=76;
  ynmp=0;
  fu=0;
  itd2=0;
  m6=0;

  while (1) {
      if (!(ynmp < vqss)) {
          break;
      }
      itd2 = itd2 + (fu += q, ynmp++, fu);
      fu = fu + 1;
      m6 = m6 + itd2;
      ynmp = vqss;
  }

}

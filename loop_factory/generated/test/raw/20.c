int main1(int t,int d,int b){
  int kz;

  kz=(b%20)+5;

  while (1) {
      if (!(kz>0)) {
          break;
      }
      kz -= 1;
      b = b + kz;
      t += 1;
      d -= 1;
  }

}

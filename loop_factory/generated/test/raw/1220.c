int main1(){
  int q, b, id, zq, pd;

  q=76;
  b=0;
  id=1;
  zq=6;
  pd=0;

  while (1) {
      if (!(pd<=q)) {
          break;
      }
      b = b + id;
      pd += 1;
      id = id + zq;
      b = b*2;
      zq += 4;
      id = id/2;
  }

}

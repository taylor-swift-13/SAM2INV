int main1(int b){
  int q, vn, waw, u, vk;

  q=b+10;
  vn=0;
  waw=b;
  u=0;
  vk=1;

  while (vn < q) {
      u = u + vk * b;
      vn = vn + 1;
      vk = -vk;
      waw = waw+(u%7);
  }

}

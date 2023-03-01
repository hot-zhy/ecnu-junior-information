# TripMap

## 简介
这是一个基于neo4j图数据库的集关注用户和收藏/点赞/发布帖子功能为一体的社交类APP；这是一个基于协同过滤算法的为用户个性化推荐在地图上的可视化打卡地点以及推荐帖子的打卡推荐类APP。在该APP中，用户不仅可以关注朋友的朋友，还可以浏览系统为其推荐的帖子，在地图上查看为其推荐的地点，点击地图上的地点还可以查看与地点相关的帖子。基于协同过滤的推荐算法，用户获得的推荐基于其关注的用户、点赞、收藏地点和帖子等行为，使用户获得较为良好的浏览体验。

## 环境

|    名称    |    版本    |
| :--------: | :--------: |
|   Server   | Centos 7.9 |
|   Neo4j    |   4.4.11   |
|   MySQL    |   8.0.31   |
|   Redis    |   3.2.12   |
|    Java    |  11.0.14   |
| SprintBoot |   2.7.5    |

## 技术栈

Spring Security

Spring Boot

Spring Data Redis

Spring Data Neo4j

Mybatis-plus

协同过滤算法

异步推荐

## 部署

在服务器配置好环境后，使用maven将项目打包通过ftp发送到服务器

## 运行

```
nohup java -jar TripMap-0.0.1-SNAPSHOT.jar &
```

### API

运行成功后可以访问`localhost:8080/api`查看系统支持的api